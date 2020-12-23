%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 129 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 ( 257 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_69,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),B_34) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    ! [A_33] : k1_tarski(A_33) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_152,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(A_59,B_60) = k1_tarski(B_60)
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_161,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_152])).

tff(c_166,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_161])).

tff(c_431,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k6_domain_1(A_78,B_79),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_445,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_431])).

tff(c_451,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_445])).

tff(c_452,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_451])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_469,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_452,c_22])).

tff(c_32,plain,(
    ! [B_29,A_27] :
      ( B_29 = A_27
      | ~ r1_tarski(A_27,B_29)
      | ~ v1_zfmisc_1(B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_472,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_469,c_32])).

tff(c_477,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_472])).

tff(c_478,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_477])).

tff(c_480,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_488,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_480,c_67])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_488])).

tff(c_497,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_181,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_36])).

tff(c_501,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_181])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1('#skF_2'(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_75,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83,plain,(
    ! [A_16] : r1_tarski('#skF_2'(A_16),A_16) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_324,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(A_72,B_71)
      | ~ v1_zfmisc_1(B_71)
      | v1_xboole_0(B_71)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2439,plain,(
    ! [A_133] :
      ( '#skF_2'(A_133) = A_133
      | ~ v1_zfmisc_1(A_133)
      | v1_xboole_0(A_133)
      | v1_xboole_0('#skF_2'(A_133)) ) ),
    inference(resolution,[status(thm)],[c_83,c_324])).

tff(c_18,plain,(
    ! [A_16] : ~ v1_subset_1('#skF_2'(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_282,plain,(
    ! [B_67,A_68] :
      ( ~ v1_xboole_0(B_67)
      | v1_subset_1(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_291,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0('#skF_2'(A_16))
      | v1_subset_1('#skF_2'(A_16),A_16)
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_282])).

tff(c_299,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0('#skF_2'(A_16))
      | v1_xboole_0(A_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_291])).

tff(c_2563,plain,(
    ! [A_136] :
      ( '#skF_2'(A_136) = A_136
      | ~ v1_zfmisc_1(A_136)
      | v1_xboole_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_2439,c_299])).

tff(c_2566,plain,
    ( '#skF_2'('#skF_3') = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2563])).

tff(c_2569,plain,(
    '#skF_2'('#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2566])).

tff(c_2663,plain,(
    ~ v1_subset_1('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_18])).

tff(c_2700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_2663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.64  
% 3.79/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.64  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.79/1.64  
% 3.79/1.64  %Foreground sorts:
% 3.79/1.64  
% 3.79/1.64  
% 3.79/1.64  %Background operators:
% 3.79/1.64  
% 3.79/1.64  
% 3.79/1.64  %Foreground operators:
% 3.79/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.79/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.79/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.79/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.79/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/1.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.79/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.79/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.79/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.64  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.79/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.79/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.64  
% 3.79/1.65  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.79/1.65  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.79/1.65  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.79/1.65  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.79/1.65  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.79/1.65  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.79/1.65  tff(f_107, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.79/1.65  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.79/1.65  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.79/1.65  tff(f_69, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.79/1.65  tff(f_63, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 3.79/1.65  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.79/1.65  tff(c_51, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.65  tff(c_55, plain, (![A_33]: (k1_tarski(A_33)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_51])).
% 3.79/1.65  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.79/1.65  tff(c_34, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.79/1.65  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.79/1.65  tff(c_152, plain, (![A_59, B_60]: (k6_domain_1(A_59, B_60)=k1_tarski(B_60) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.79/1.65  tff(c_161, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_152])).
% 3.79/1.65  tff(c_166, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_161])).
% 3.79/1.65  tff(c_431, plain, (![A_78, B_79]: (m1_subset_1(k6_domain_1(A_78, B_79), k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.79/1.65  tff(c_445, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_166, c_431])).
% 3.79/1.65  tff(c_451, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_445])).
% 3.79/1.65  tff(c_452, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_451])).
% 3.79/1.65  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/1.65  tff(c_469, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_452, c_22])).
% 3.79/1.65  tff(c_32, plain, (![B_29, A_27]: (B_29=A_27 | ~r1_tarski(A_27, B_29) | ~v1_zfmisc_1(B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.65  tff(c_472, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_469, c_32])).
% 3.79/1.65  tff(c_477, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_472])).
% 3.79/1.65  tff(c_478, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_477])).
% 3.79/1.65  tff(c_480, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_478])).
% 3.79/1.65  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/1.65  tff(c_64, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.79/1.65  tff(c_67, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_6, c_64])).
% 3.79/1.65  tff(c_488, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_480, c_67])).
% 3.79/1.65  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_488])).
% 3.79/1.65  tff(c_497, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_478])).
% 3.79/1.65  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.79/1.65  tff(c_181, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_36])).
% 3.79/1.65  tff(c_501, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_181])).
% 3.79/1.65  tff(c_20, plain, (![A_16]: (m1_subset_1('#skF_2'(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/1.65  tff(c_75, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/1.66  tff(c_83, plain, (![A_16]: (r1_tarski('#skF_2'(A_16), A_16))), inference(resolution, [status(thm)], [c_20, c_75])).
% 3.79/1.66  tff(c_324, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(A_72, B_71) | ~v1_zfmisc_1(B_71) | v1_xboole_0(B_71) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.66  tff(c_2439, plain, (![A_133]: ('#skF_2'(A_133)=A_133 | ~v1_zfmisc_1(A_133) | v1_xboole_0(A_133) | v1_xboole_0('#skF_2'(A_133)))), inference(resolution, [status(thm)], [c_83, c_324])).
% 3.79/1.66  tff(c_18, plain, (![A_16]: (~v1_subset_1('#skF_2'(A_16), A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/1.66  tff(c_282, plain, (![B_67, A_68]: (~v1_xboole_0(B_67) | v1_subset_1(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.79/1.66  tff(c_291, plain, (![A_16]: (~v1_xboole_0('#skF_2'(A_16)) | v1_subset_1('#skF_2'(A_16), A_16) | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_282])).
% 3.79/1.66  tff(c_299, plain, (![A_16]: (~v1_xboole_0('#skF_2'(A_16)) | v1_xboole_0(A_16))), inference(negUnitSimplification, [status(thm)], [c_18, c_291])).
% 3.79/1.66  tff(c_2563, plain, (![A_136]: ('#skF_2'(A_136)=A_136 | ~v1_zfmisc_1(A_136) | v1_xboole_0(A_136))), inference(resolution, [status(thm)], [c_2439, c_299])).
% 3.79/1.66  tff(c_2566, plain, ('#skF_2'('#skF_3')='#skF_3' | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2563])).
% 3.79/1.66  tff(c_2569, plain, ('#skF_2'('#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_2566])).
% 3.79/1.66  tff(c_2663, plain, (~v1_subset_1('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2569, c_18])).
% 3.79/1.66  tff(c_2700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_2663])).
% 3.79/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.66  
% 3.79/1.66  Inference rules
% 3.79/1.66  ----------------------
% 3.79/1.66  #Ref     : 0
% 3.79/1.66  #Sup     : 622
% 3.79/1.66  #Fact    : 0
% 3.79/1.66  #Define  : 0
% 3.79/1.66  #Split   : 7
% 3.79/1.66  #Chain   : 0
% 3.79/1.66  #Close   : 0
% 3.79/1.66  
% 3.79/1.66  Ordering : KBO
% 3.79/1.66  
% 3.79/1.66  Simplification rules
% 3.79/1.66  ----------------------
% 3.79/1.66  #Subsume      : 195
% 3.79/1.66  #Demod        : 536
% 3.79/1.66  #Tautology    : 238
% 3.79/1.66  #SimpNegUnit  : 55
% 3.79/1.66  #BackRed      : 13
% 3.79/1.66  
% 3.79/1.66  #Partial instantiations: 0
% 3.79/1.66  #Strategies tried      : 1
% 3.79/1.66  
% 3.79/1.66  Timing (in seconds)
% 3.79/1.66  ----------------------
% 3.79/1.66  Preprocessing        : 0.30
% 3.79/1.66  Parsing              : 0.17
% 3.79/1.66  CNF conversion       : 0.02
% 3.79/1.66  Main loop            : 0.59
% 3.79/1.66  Inferencing          : 0.20
% 3.79/1.66  Reduction            : 0.19
% 3.79/1.66  Demodulation         : 0.14
% 3.79/1.66  BG Simplification    : 0.02
% 3.79/1.66  Subsumption          : 0.13
% 3.79/1.66  Abstraction          : 0.03
% 3.79/1.66  MUC search           : 0.00
% 3.79/1.66  Cooper               : 0.00
% 3.79/1.66  Total                : 0.93
% 3.79/1.66  Index Insertion      : 0.00
% 3.79/1.66  Index Deletion       : 0.00
% 3.79/1.66  Index Matching       : 0.00
% 3.79/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
