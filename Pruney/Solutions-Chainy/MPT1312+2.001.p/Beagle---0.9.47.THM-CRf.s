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
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   64 (  78 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 139 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_118,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1984,plain,(
    ! [A_259,B_260,B_261] :
      ( r2_hidden('#skF_1'(A_259,B_260),B_261)
      | ~ r1_tarski(A_259,B_261)
      | r1_tarski(A_259,B_260) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_125,plain,(
    ! [A_57,C_58,B_59] :
      ( m1_subset_1(A_57,C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    ! [A_57,B_16,A_15] :
      ( m1_subset_1(A_57,B_16)
      | ~ r2_hidden(A_57,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_125])).

tff(c_2502,plain,(
    ! [A_320,B_321,B_322,B_323] :
      ( m1_subset_1('#skF_1'(A_320,B_321),B_322)
      | ~ r1_tarski(B_323,B_322)
      | ~ r1_tarski(A_320,B_323)
      | r1_tarski(A_320,B_321) ) ),
    inference(resolution,[status(thm)],[c_1984,c_132])).

tff(c_2572,plain,(
    ! [A_329,B_330] :
      ( m1_subset_1('#skF_1'(A_329,B_330),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_329,'#skF_4')
      | r1_tarski(A_329,B_330) ) ),
    inference(resolution,[status(thm)],[c_72,c_2502])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2596,plain,(
    ! [A_329,B_330] :
      ( r1_tarski('#skF_1'(A_329,B_330),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_329,'#skF_4')
      | r1_tarski(A_329,B_330) ) ),
    inference(resolution,[status(thm)],[c_2572,c_18])).

tff(c_12,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_20] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ! [B_49,A_50] :
      ( v1_xboole_0(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,(
    ! [A_20] :
      ( v1_xboole_0(k1_tarski(k1_xboole_0))
      | ~ v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_101,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_94])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_158,plain,(
    ! [C_63,A_64,B_65] :
      ( m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(B_65)))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2161,plain,(
    ! [A_279,A_280,B_281] :
      ( m1_subset_1(A_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_pre_topc(B_281,A_280)
      | ~ l1_pre_topc(A_280)
      | ~ r1_tarski(A_279,u1_struct_0(B_281)) ) ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_2163,plain,(
    ! [A_279] :
      ( m1_subset_1(A_279,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_279,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_2161])).

tff(c_2167,plain,(
    ! [A_282] :
      ( m1_subset_1(A_282,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_282,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2163])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    ! [A_46,B_14] :
      ( r1_tarski(A_46,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1('#skF_1'(A_46,B_14),B_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_2171,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_1'(A_46,k1_zfmisc_1(u1_struct_0('#skF_2'))),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2167,c_85])).

tff(c_2673,plain,(
    ! [A_343] :
      ( r1_tarski(A_343,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_1'(A_343,k1_zfmisc_1(u1_struct_0('#skF_2'))),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_2171])).

tff(c_2703,plain,(
    ! [A_344] :
      ( ~ r1_tarski(A_344,'#skF_4')
      | r1_tarski(A_344,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_2596,c_2673])).

tff(c_46,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_46,c_28])).

tff(c_2729,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2703,c_50])).

tff(c_2742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.85  
% 4.57/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.85  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.57/1.85  
% 4.57/1.85  %Foreground sorts:
% 4.57/1.85  
% 4.57/1.85  
% 4.57/1.85  %Background operators:
% 4.57/1.85  
% 4.57/1.85  
% 4.57/1.85  %Foreground operators:
% 4.57/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.57/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.57/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.57/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.57/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.57/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.57/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.57/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.85  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.57/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.57/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.85  
% 4.57/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.57/1.87  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 4.57/1.87  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.57/1.87  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.57/1.87  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.57/1.87  tff(f_64, axiom, (![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 4.57/1.87  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.57/1.87  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.57/1.87  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.57/1.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.57/1.87  tff(c_76, plain, (![A_46, B_47]: (~r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.57/1.87  tff(c_86, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_76])).
% 4.57/1.87  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.57/1.87  tff(c_60, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.57/1.87  tff(c_72, plain, (r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_30, c_60])).
% 4.57/1.87  tff(c_118, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.57/1.87  tff(c_1984, plain, (![A_259, B_260, B_261]: (r2_hidden('#skF_1'(A_259, B_260), B_261) | ~r1_tarski(A_259, B_261) | r1_tarski(A_259, B_260))), inference(resolution, [status(thm)], [c_6, c_118])).
% 4.57/1.87  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.57/1.87  tff(c_125, plain, (![A_57, C_58, B_59]: (m1_subset_1(A_57, C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.57/1.87  tff(c_132, plain, (![A_57, B_16, A_15]: (m1_subset_1(A_57, B_16) | ~r2_hidden(A_57, A_15) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_20, c_125])).
% 4.57/1.87  tff(c_2502, plain, (![A_320, B_321, B_322, B_323]: (m1_subset_1('#skF_1'(A_320, B_321), B_322) | ~r1_tarski(B_323, B_322) | ~r1_tarski(A_320, B_323) | r1_tarski(A_320, B_321))), inference(resolution, [status(thm)], [c_1984, c_132])).
% 4.57/1.87  tff(c_2572, plain, (![A_329, B_330]: (m1_subset_1('#skF_1'(A_329, B_330), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_329, '#skF_4') | r1_tarski(A_329, B_330))), inference(resolution, [status(thm)], [c_72, c_2502])).
% 4.57/1.87  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.57/1.87  tff(c_2596, plain, (![A_329, B_330]: (r1_tarski('#skF_1'(A_329, B_330), u1_struct_0('#skF_3')) | ~r1_tarski(A_329, '#skF_4') | r1_tarski(A_329, B_330))), inference(resolution, [status(thm)], [c_2572, c_18])).
% 4.57/1.87  tff(c_12, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.57/1.87  tff(c_24, plain, (![A_20]: (m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.57/1.87  tff(c_88, plain, (![B_49, A_50]: (v1_xboole_0(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.57/1.87  tff(c_94, plain, (![A_20]: (v1_xboole_0(k1_tarski(k1_xboole_0)) | ~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_24, c_88])).
% 4.57/1.87  tff(c_101, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(negUnitSimplification, [status(thm)], [c_12, c_94])).
% 4.57/1.87  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.57/1.87  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.57/1.87  tff(c_158, plain, (![C_63, A_64, B_65]: (m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(B_65))) | ~m1_pre_topc(B_65, A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.57/1.87  tff(c_2161, plain, (![A_279, A_280, B_281]: (m1_subset_1(A_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_pre_topc(B_281, A_280) | ~l1_pre_topc(A_280) | ~r1_tarski(A_279, u1_struct_0(B_281)))), inference(resolution, [status(thm)], [c_20, c_158])).
% 4.57/1.87  tff(c_2163, plain, (![A_279]: (m1_subset_1(A_279, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_279, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_2161])).
% 4.57/1.87  tff(c_2167, plain, (![A_282]: (m1_subset_1(A_282, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_282, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2163])).
% 4.57/1.87  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.57/1.87  tff(c_85, plain, (![A_46, B_14]: (r1_tarski(A_46, B_14) | v1_xboole_0(B_14) | ~m1_subset_1('#skF_1'(A_46, B_14), B_14))), inference(resolution, [status(thm)], [c_16, c_76])).
% 4.57/1.87  tff(c_2171, plain, (![A_46]: (r1_tarski(A_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_1'(A_46, k1_zfmisc_1(u1_struct_0('#skF_2'))), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2167, c_85])).
% 4.57/1.87  tff(c_2673, plain, (![A_343]: (r1_tarski(A_343, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_1'(A_343, k1_zfmisc_1(u1_struct_0('#skF_2'))), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_101, c_2171])).
% 4.57/1.87  tff(c_2703, plain, (![A_344]: (~r1_tarski(A_344, '#skF_4') | r1_tarski(A_344, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_2596, c_2673])).
% 4.57/1.87  tff(c_46, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.57/1.87  tff(c_28, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.57/1.87  tff(c_50, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_46, c_28])).
% 4.57/1.87  tff(c_2729, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2703, c_50])).
% 4.57/1.87  tff(c_2742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_2729])).
% 4.57/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.87  
% 4.57/1.87  Inference rules
% 4.57/1.87  ----------------------
% 4.57/1.87  #Ref     : 0
% 4.57/1.87  #Sup     : 696
% 4.57/1.87  #Fact    : 0
% 4.57/1.87  #Define  : 0
% 4.57/1.87  #Split   : 22
% 4.57/1.87  #Chain   : 0
% 4.57/1.87  #Close   : 0
% 4.57/1.87  
% 4.57/1.87  Ordering : KBO
% 4.57/1.87  
% 4.57/1.87  Simplification rules
% 4.57/1.87  ----------------------
% 4.57/1.87  #Subsume      : 260
% 4.57/1.87  #Demod        : 21
% 4.57/1.87  #Tautology    : 28
% 4.57/1.87  #SimpNegUnit  : 41
% 4.57/1.87  #BackRed      : 8
% 4.57/1.87  
% 4.57/1.87  #Partial instantiations: 0
% 4.57/1.87  #Strategies tried      : 1
% 4.57/1.87  
% 4.57/1.87  Timing (in seconds)
% 4.57/1.87  ----------------------
% 4.57/1.87  Preprocessing        : 0.30
% 4.57/1.87  Parsing              : 0.16
% 4.57/1.87  CNF conversion       : 0.02
% 4.57/1.87  Main loop            : 0.78
% 4.57/1.87  Inferencing          : 0.27
% 4.57/1.87  Reduction            : 0.22
% 4.57/1.87  Demodulation         : 0.13
% 4.57/1.87  BG Simplification    : 0.03
% 4.57/1.87  Subsumption          : 0.20
% 4.57/1.87  Abstraction          : 0.03
% 4.57/1.87  MUC search           : 0.00
% 4.57/1.87  Cooper               : 0.00
% 4.57/1.87  Total                : 1.11
% 4.57/1.87  Index Insertion      : 0.00
% 4.57/1.87  Index Deletion       : 0.00
% 4.57/1.87  Index Matching       : 0.00
% 4.57/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
