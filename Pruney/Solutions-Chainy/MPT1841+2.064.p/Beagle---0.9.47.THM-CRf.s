%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:36 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   69 (  88 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 136 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_34,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_122,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_122])).

tff(c_134,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_131])).

tff(c_146,plain,(
    ! [D_56,B_57,A_58] :
      ( ~ r2_hidden(D_56,B_57)
      | ~ r2_hidden(D_56,k4_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [D_61,A_62] :
      ( ~ r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_146])).

tff(c_172,plain,(
    ! [C_19] : ~ r2_hidden(C_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_166])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_62,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_182,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_182])).

tff(c_188,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_185])).

tff(c_60,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_189,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_60])).

tff(c_194,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k6_domain_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_203,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_194])).

tff(c_207,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_203])).

tff(c_208,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_207])).

tff(c_1249,plain,(
    ! [B_1624,A_1625] :
      ( ~ v1_subset_1(B_1624,A_1625)
      | v1_xboole_0(B_1624)
      | ~ m1_subset_1(B_1624,k1_zfmisc_1(A_1625))
      | ~ v1_zfmisc_1(A_1625)
      | v1_xboole_0(A_1625) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1256,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_6'),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_208,c_1249])).

tff(c_1263,plain,
    ( v1_xboole_0(k1_tarski('#skF_6'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_189,c_1256])).

tff(c_1264,plain,(
    v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1263])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | B_42 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_1304,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1264,c_94])).

tff(c_1327,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_34])).

tff(c_1365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_1327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:49:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.50  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.30/1.50  
% 3.30/1.50  %Foreground sorts:
% 3.30/1.50  
% 3.30/1.50  
% 3.30/1.50  %Background operators:
% 3.30/1.50  
% 3.30/1.50  
% 3.30/1.50  %Foreground operators:
% 3.30/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.30/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.30/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.30/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.30/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.30/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.30/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.30/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.30/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.50  
% 3.30/1.52  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.30/1.52  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.30/1.52  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.30/1.52  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.30/1.52  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.30/1.52  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.30/1.52  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.30/1.52  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.30/1.52  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.30/1.52  tff(f_107, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.30/1.52  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.30/1.52  tff(f_54, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.30/1.52  tff(c_34, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.30/1.52  tff(c_28, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.52  tff(c_26, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.30/1.52  tff(c_101, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.30/1.52  tff(c_105, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_101])).
% 3.30/1.52  tff(c_122, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.30/1.52  tff(c_131, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_105, c_122])).
% 3.30/1.52  tff(c_134, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_131])).
% 3.30/1.52  tff(c_146, plain, (![D_56, B_57, A_58]: (~r2_hidden(D_56, B_57) | ~r2_hidden(D_56, k4_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.52  tff(c_166, plain, (![D_61, A_62]: (~r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_134, c_146])).
% 3.30/1.52  tff(c_172, plain, (![C_19]: (~r2_hidden(C_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_166])).
% 3.30/1.52  tff(c_64, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.52  tff(c_58, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.52  tff(c_62, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.52  tff(c_182, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.30/1.52  tff(c_185, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_182])).
% 3.30/1.52  tff(c_188, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_185])).
% 3.30/1.52  tff(c_60, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.52  tff(c_189, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_60])).
% 3.30/1.52  tff(c_194, plain, (![A_70, B_71]: (m1_subset_1(k6_domain_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.30/1.52  tff(c_203, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_188, c_194])).
% 3.30/1.52  tff(c_207, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_203])).
% 3.30/1.52  tff(c_208, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_207])).
% 3.30/1.52  tff(c_1249, plain, (![B_1624, A_1625]: (~v1_subset_1(B_1624, A_1625) | v1_xboole_0(B_1624) | ~m1_subset_1(B_1624, k1_zfmisc_1(A_1625)) | ~v1_zfmisc_1(A_1625) | v1_xboole_0(A_1625))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.30/1.52  tff(c_1256, plain, (~v1_subset_1(k1_tarski('#skF_6'), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_208, c_1249])).
% 3.30/1.52  tff(c_1263, plain, (v1_xboole_0(k1_tarski('#skF_6')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_189, c_1256])).
% 3.30/1.52  tff(c_1264, plain, (v1_xboole_0(k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1263])).
% 3.30/1.52  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.30/1.52  tff(c_91, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | B_42=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.30/1.52  tff(c_94, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_20, c_91])).
% 3.30/1.52  tff(c_1304, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1264, c_94])).
% 3.30/1.52  tff(c_1327, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1304, c_34])).
% 3.30/1.52  tff(c_1365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_1327])).
% 3.30/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  Inference rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Ref     : 0
% 3.30/1.52  #Sup     : 165
% 3.30/1.52  #Fact    : 0
% 3.30/1.52  #Define  : 0
% 3.30/1.52  #Split   : 4
% 3.30/1.52  #Chain   : 0
% 3.30/1.52  #Close   : 0
% 3.30/1.52  
% 3.30/1.52  Ordering : KBO
% 3.30/1.52  
% 3.30/1.52  Simplification rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Subsume      : 29
% 3.30/1.52  #Demod        : 68
% 3.30/1.52  #Tautology    : 68
% 3.30/1.52  #SimpNegUnit  : 18
% 3.30/1.52  #BackRed      : 15
% 3.30/1.52  
% 3.30/1.52  #Partial instantiations: 930
% 3.30/1.52  #Strategies tried      : 1
% 3.30/1.52  
% 3.30/1.52  Timing (in seconds)
% 3.30/1.52  ----------------------
% 3.30/1.52  Preprocessing        : 0.33
% 3.30/1.52  Parsing              : 0.17
% 3.30/1.52  CNF conversion       : 0.02
% 3.30/1.52  Main loop            : 0.41
% 3.30/1.52  Inferencing          : 0.20
% 3.30/1.52  Reduction            : 0.10
% 3.30/1.52  Demodulation         : 0.07
% 3.30/1.52  BG Simplification    : 0.02
% 3.30/1.52  Subsumption          : 0.06
% 3.30/1.52  Abstraction          : 0.02
% 3.30/1.52  MUC search           : 0.00
% 3.30/1.52  Cooper               : 0.00
% 3.30/1.52  Total                : 0.77
% 3.30/1.52  Index Insertion      : 0.00
% 3.30/1.52  Index Deletion       : 0.00
% 3.30/1.52  Index Matching       : 0.00
% 3.30/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
