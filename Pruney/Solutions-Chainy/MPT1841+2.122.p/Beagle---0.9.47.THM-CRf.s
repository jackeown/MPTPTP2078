%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [C_61,B_62,A_63] :
      ( ~ v1_xboole_0(C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_158,plain,(
    ! [B_64,A_65,A_66] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(A_65,A_66)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_165,plain,(
    ! [B_67,C_68] :
      ( ~ v1_xboole_0(B_67)
      | ~ r1_tarski(k1_tarski(C_68),B_67) ) ),
    inference(resolution,[status(thm)],[c_18,c_158])).

tff(c_170,plain,(
    ! [C_68] : ~ v1_xboole_0(k1_tarski(C_68)) ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_172,plain,(
    ! [A_70,B_71] :
      ( k6_domain_1(A_70,B_71) = k1_tarski(B_71)
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_172])).

tff(c_182,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_178])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_183,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_48])).

tff(c_196,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k6_domain_1(A_75,B_76),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_207,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_196])).

tff(c_212,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_207])).

tff(c_213,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_212])).

tff(c_1294,plain,(
    ! [B_150,A_151] :
      ( ~ v1_subset_1(B_150,A_151)
      | v1_xboole_0(B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_151))
      | ~ v1_zfmisc_1(A_151)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1300,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_5'),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_213,c_1294])).

tff(c_1312,plain,
    ( v1_xboole_0(k1_tarski('#skF_5'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_183,c_1300])).

tff(c_1314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_170,c_1312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.51  
% 3.17/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.52  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.17/1.52  
% 3.17/1.52  %Foreground sorts:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Background operators:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Foreground operators:
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.52  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.17/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.17/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.17/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.17/1.52  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.17/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.52  
% 3.17/1.53  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.17/1.53  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.53  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.17/1.53  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.53  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.17/1.53  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.17/1.53  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.17/1.53  tff(f_95, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.17/1.53  tff(c_52, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.53  tff(c_18, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.53  tff(c_34, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.53  tff(c_154, plain, (![C_61, B_62, A_63]: (~v1_xboole_0(C_61) | ~m1_subset_1(B_62, k1_zfmisc_1(C_61)) | ~r2_hidden(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.53  tff(c_158, plain, (![B_64, A_65, A_66]: (~v1_xboole_0(B_64) | ~r2_hidden(A_65, A_66) | ~r1_tarski(A_66, B_64))), inference(resolution, [status(thm)], [c_34, c_154])).
% 3.17/1.53  tff(c_165, plain, (![B_67, C_68]: (~v1_xboole_0(B_67) | ~r1_tarski(k1_tarski(C_68), B_67))), inference(resolution, [status(thm)], [c_18, c_158])).
% 3.17/1.53  tff(c_170, plain, (![C_68]: (~v1_xboole_0(k1_tarski(C_68)))), inference(resolution, [status(thm)], [c_12, c_165])).
% 3.17/1.53  tff(c_46, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_50, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_172, plain, (![A_70, B_71]: (k6_domain_1(A_70, B_71)=k1_tarski(B_71) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.53  tff(c_178, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_172])).
% 3.17/1.53  tff(c_182, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_178])).
% 3.17/1.53  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_183, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_48])).
% 3.17/1.53  tff(c_196, plain, (![A_75, B_76]: (m1_subset_1(k6_domain_1(A_75, B_76), k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.53  tff(c_207, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_182, c_196])).
% 3.17/1.53  tff(c_212, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_207])).
% 3.17/1.53  tff(c_213, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_212])).
% 3.17/1.53  tff(c_1294, plain, (![B_150, A_151]: (~v1_subset_1(B_150, A_151) | v1_xboole_0(B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(A_151)) | ~v1_zfmisc_1(A_151) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.17/1.53  tff(c_1300, plain, (~v1_subset_1(k1_tarski('#skF_5'), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_213, c_1294])).
% 3.17/1.53  tff(c_1312, plain, (v1_xboole_0(k1_tarski('#skF_5')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_183, c_1300])).
% 3.17/1.53  tff(c_1314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_170, c_1312])).
% 3.17/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  Inference rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Ref     : 0
% 3.17/1.53  #Sup     : 288
% 3.17/1.53  #Fact    : 0
% 3.17/1.53  #Define  : 0
% 3.17/1.53  #Split   : 3
% 3.17/1.53  #Chain   : 0
% 3.17/1.53  #Close   : 0
% 3.17/1.53  
% 3.17/1.53  Ordering : KBO
% 3.17/1.53  
% 3.17/1.53  Simplification rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Subsume      : 85
% 3.17/1.53  #Demod        : 41
% 3.17/1.53  #Tautology    : 88
% 3.17/1.53  #SimpNegUnit  : 18
% 3.17/1.53  #BackRed      : 3
% 3.17/1.53  
% 3.17/1.53  #Partial instantiations: 0
% 3.17/1.53  #Strategies tried      : 1
% 3.17/1.53  
% 3.17/1.53  Timing (in seconds)
% 3.17/1.53  ----------------------
% 3.17/1.53  Preprocessing        : 0.30
% 3.17/1.53  Parsing              : 0.15
% 3.17/1.53  CNF conversion       : 0.02
% 3.17/1.53  Main loop            : 0.43
% 3.17/1.53  Inferencing          : 0.15
% 3.17/1.53  Reduction            : 0.12
% 3.17/1.53  Demodulation         : 0.08
% 3.17/1.53  BG Simplification    : 0.02
% 3.17/1.53  Subsumption          : 0.10
% 3.17/1.53  Abstraction          : 0.02
% 3.17/1.53  MUC search           : 0.00
% 3.17/1.53  Cooper               : 0.00
% 3.17/1.53  Total                : 0.75
% 3.17/1.53  Index Insertion      : 0.00
% 3.17/1.53  Index Deletion       : 0.00
% 3.17/1.53  Index Matching       : 0.00
% 3.17/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
