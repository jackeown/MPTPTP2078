%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 40.92s
% Output     : CNFRefutation 41.05s
% Verified   : 
% Statistics : Number of formulae       :   58 (  81 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 162 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_46,plain,(
    v3_setfam_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_98,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden(A_51,B_52)
      | ~ v3_setfam_1(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_101,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v3_setfam_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_101])).

tff(c_42,plain,(
    v3_setfam_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_104])).

tff(c_268,plain,(
    ! [A_85,B_86,C_87] :
      ( k4_subset_1(A_85,B_86,C_87) = k2_xboole_0(B_86,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_340,plain,(
    ! [B_89] :
      ( k4_subset_1(k1_zfmisc_1('#skF_2'),B_89,'#skF_4') = k2_xboole_0(B_89,'#skF_4')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_268])).

tff(c_360,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_340])).

tff(c_38,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_362,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_38])).

tff(c_30,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k4_subset_1(A_20,B_21,C_22),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_366,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_30])).

tff(c_370,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_366])).

tff(c_34,plain,(
    ! [B_27,A_26] :
      ( v3_setfam_1(B_27,A_26)
      | r2_hidden(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_382,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_3','#skF_4'),'#skF_2')
    | r2_hidden('#skF_2',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_370,c_34])).

tff(c_391,plain,(
    r2_hidden('#skF_2',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_382])).

tff(c_20,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(A_59,B_60)
      | r2_hidden(A_59,C_61)
      | ~ r2_hidden(A_59,k5_xboole_0(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [A_70,A_71,B_72] :
      ( r2_hidden(A_70,A_71)
      | r2_hidden(A_70,k4_xboole_0(B_72,A_71))
      | ~ r2_hidden(A_70,k2_xboole_0(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_135])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224687,plain,(
    ! [A_10763,B_10764,B_10765,A_10766] :
      ( r2_hidden(A_10763,B_10764)
      | ~ r1_tarski(k4_xboole_0(B_10765,A_10766),B_10764)
      | r2_hidden(A_10763,A_10766)
      | ~ r2_hidden(A_10763,k2_xboole_0(A_10766,B_10765)) ) ),
    inference(resolution,[status(thm)],[c_201,c_2])).

tff(c_224695,plain,(
    ! [A_10767,A_10768,B_10769] :
      ( r2_hidden(A_10767,A_10768)
      | r2_hidden(A_10767,B_10769)
      | ~ r2_hidden(A_10767,k2_xboole_0(B_10769,A_10768)) ) ),
    inference(resolution,[status(thm)],[c_20,c_224687])).

tff(c_224755,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_391,c_224695])).

tff(c_224786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_110,c_224755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.92/31.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.92/31.59  
% 40.92/31.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.92/31.59  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 40.92/31.59  
% 40.92/31.59  %Foreground sorts:
% 40.92/31.59  
% 40.92/31.59  
% 40.92/31.59  %Background operators:
% 40.92/31.59  
% 40.92/31.59  
% 40.92/31.59  %Foreground operators:
% 40.92/31.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.92/31.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.92/31.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 40.92/31.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 40.92/31.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.92/31.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 40.92/31.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 40.92/31.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 40.92/31.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 40.92/31.59  tff('#skF_2', type, '#skF_2': $i).
% 40.92/31.59  tff('#skF_3', type, '#skF_3': $i).
% 40.92/31.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.92/31.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.92/31.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 40.92/31.59  tff('#skF_4', type, '#skF_4': $i).
% 40.92/31.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.92/31.59  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 40.92/31.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 40.92/31.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 40.92/31.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 40.92/31.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.92/31.59  
% 41.05/31.60  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_setfam_1)).
% 41.05/31.60  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 41.05/31.60  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 41.05/31.60  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 41.05/31.60  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 41.05/31.60  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 41.05/31.60  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 41.05/31.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 41.05/31.60  tff(c_46, plain, (v3_setfam_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.05/31.60  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.05/31.60  tff(c_98, plain, (![A_51, B_52]: (~r2_hidden(A_51, B_52) | ~v3_setfam_1(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 41.05/31.60  tff(c_101, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v3_setfam_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_98])).
% 41.05/31.60  tff(c_107, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_101])).
% 41.05/31.60  tff(c_42, plain, (v3_setfam_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.05/31.60  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.05/31.60  tff(c_104, plain, (~r2_hidden('#skF_2', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_98])).
% 41.05/31.60  tff(c_110, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_104])).
% 41.05/31.60  tff(c_268, plain, (![A_85, B_86, C_87]: (k4_subset_1(A_85, B_86, C_87)=k2_xboole_0(B_86, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(A_85)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.05/31.60  tff(c_340, plain, (![B_89]: (k4_subset_1(k1_zfmisc_1('#skF_2'), B_89, '#skF_4')=k2_xboole_0(B_89, '#skF_4') | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_40, c_268])).
% 41.05/31.60  tff(c_360, plain, (k4_subset_1(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_340])).
% 41.05/31.60  tff(c_38, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.05/31.60  tff(c_362, plain, (~v3_setfam_1(k2_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_38])).
% 41.05/31.60  tff(c_30, plain, (![A_20, B_21, C_22]: (m1_subset_1(k4_subset_1(A_20, B_21, C_22), k1_zfmisc_1(A_20)) | ~m1_subset_1(C_22, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 41.05/31.60  tff(c_366, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_360, c_30])).
% 41.05/31.60  tff(c_370, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_366])).
% 41.05/31.60  tff(c_34, plain, (![B_27, A_26]: (v3_setfam_1(B_27, A_26) | r2_hidden(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 41.05/31.60  tff(c_382, plain, (v3_setfam_1(k2_xboole_0('#skF_3', '#skF_4'), '#skF_2') | r2_hidden('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_370, c_34])).
% 41.05/31.60  tff(c_391, plain, (r2_hidden('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_362, c_382])).
% 41.05/31.60  tff(c_20, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.05/31.60  tff(c_22, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 41.05/31.60  tff(c_135, plain, (![A_59, B_60, C_61]: (r2_hidden(A_59, B_60) | r2_hidden(A_59, C_61) | ~r2_hidden(A_59, k5_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 41.05/31.60  tff(c_201, plain, (![A_70, A_71, B_72]: (r2_hidden(A_70, A_71) | r2_hidden(A_70, k4_xboole_0(B_72, A_71)) | ~r2_hidden(A_70, k2_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_135])).
% 41.05/31.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 41.05/31.60  tff(c_224687, plain, (![A_10763, B_10764, B_10765, A_10766]: (r2_hidden(A_10763, B_10764) | ~r1_tarski(k4_xboole_0(B_10765, A_10766), B_10764) | r2_hidden(A_10763, A_10766) | ~r2_hidden(A_10763, k2_xboole_0(A_10766, B_10765)))), inference(resolution, [status(thm)], [c_201, c_2])).
% 41.05/31.60  tff(c_224695, plain, (![A_10767, A_10768, B_10769]: (r2_hidden(A_10767, A_10768) | r2_hidden(A_10767, B_10769) | ~r2_hidden(A_10767, k2_xboole_0(B_10769, A_10768)))), inference(resolution, [status(thm)], [c_20, c_224687])).
% 41.05/31.60  tff(c_224755, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_391, c_224695])).
% 41.05/31.60  tff(c_224786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_110, c_224755])).
% 41.05/31.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.05/31.60  
% 41.05/31.60  Inference rules
% 41.05/31.60  ----------------------
% 41.05/31.60  #Ref     : 0
% 41.05/31.60  #Sup     : 52300
% 41.05/31.60  #Fact    : 44
% 41.05/31.60  #Define  : 0
% 41.05/31.60  #Split   : 1235
% 41.05/31.60  #Chain   : 0
% 41.05/31.60  #Close   : 0
% 41.05/31.60  
% 41.05/31.60  Ordering : KBO
% 41.05/31.60  
% 41.05/31.60  Simplification rules
% 41.05/31.60  ----------------------
% 41.05/31.60  #Subsume      : 4852
% 41.05/31.60  #Demod        : 41838
% 41.05/31.60  #Tautology    : 7321
% 41.05/31.60  #SimpNegUnit  : 4667
% 41.05/31.60  #BackRed      : 1
% 41.05/31.60  
% 41.05/31.60  #Partial instantiations: 0
% 41.05/31.60  #Strategies tried      : 1
% 41.05/31.60  
% 41.05/31.60  Timing (in seconds)
% 41.05/31.60  ----------------------
% 41.05/31.61  Preprocessing        : 0.31
% 41.05/31.61  Parsing              : 0.16
% 41.05/31.61  CNF conversion       : 0.02
% 41.05/31.61  Main loop            : 30.54
% 41.05/31.61  Inferencing          : 7.42
% 41.05/31.61  Reduction            : 12.95
% 41.05/31.61  Demodulation         : 9.97
% 41.05/31.61  BG Simplification    : 0.55
% 41.05/31.61  Subsumption          : 7.71
% 41.05/31.61  Abstraction          : 1.09
% 41.05/31.61  MUC search           : 0.00
% 41.05/31.61  Cooper               : 0.00
% 41.05/31.61  Total                : 30.88
% 41.05/31.61  Index Insertion      : 0.00
% 41.05/31.61  Index Deletion       : 0.00
% 41.05/31.61  Index Matching       : 0.00
% 41.05/31.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
