%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:47 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 122 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_45,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_103,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_74,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_53,c_103])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
    ! [A_96,A_97] :
      ( r1_tarski(A_96,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_96,A_97)
      | ~ r1_tarski(A_97,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_116,c_10])).

tff(c_917,plain,(
    ! [A_200,C_201,B_202] :
      ( r1_tarski(k3_xboole_0(A_200,C_201),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_202,'#skF_2')
      | ~ r1_tarski(A_200,B_202) ) ),
    inference(resolution,[status(thm)],[c_8,c_230])).

tff(c_941,plain,(
    ! [A_200,C_201] :
      ( r1_tarski(k3_xboole_0(A_200,C_201),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_200,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_917])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1005,plain,(
    ! [B_210,A_211,C_212] :
      ( v1_tops_2(B_210,A_211)
      | ~ v1_tops_2(C_212,A_211)
      | ~ r1_tarski(B_210,C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211))))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211))))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1217,plain,(
    ! [A_229,C_230,A_231,B_232] :
      ( v1_tops_2(k3_xboole_0(A_229,C_230),A_231)
      | ~ v1_tops_2(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_231))))
      | ~ m1_subset_1(k3_xboole_0(A_229,C_230),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_231))))
      | ~ l1_pre_topc(A_231)
      | ~ r1_tarski(A_229,B_232) ) ),
    inference(resolution,[status(thm)],[c_8,c_1005])).

tff(c_1224,plain,(
    ! [A_229,C_230] :
      ( v1_tops_2(k3_xboole_0(A_229,C_230),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1(k3_xboole_0(A_229,C_230),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_229,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1217])).

tff(c_1301,plain,(
    ! [A_241,C_242] :
      ( v1_tops_2(k3_xboole_0(A_241,C_242),'#skF_1')
      | ~ m1_subset_1(k3_xboole_0(A_241,C_242),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_241,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_1224])).

tff(c_1828,plain,(
    ! [A_306,C_307] :
      ( v1_tops_2(k3_xboole_0(A_306,C_307),'#skF_1')
      | ~ r1_tarski(A_306,'#skF_2')
      | ~ r1_tarski(k3_xboole_0(A_306,C_307),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_1301])).

tff(c_1924,plain,(
    ! [A_308,C_309] :
      ( v1_tops_2(k3_xboole_0(A_308,C_309),'#skF_1')
      | ~ r1_tarski(A_308,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_941,c_1828])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_132,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,C_78) = k3_xboole_0(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_140,plain,(
    ! [B_77] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_77,'#skF_3') = k3_xboole_0(B_77,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_34,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_142,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_34])).

tff(c_1927,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1924,c_142])).

tff(c_1931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/2.37  
% 5.38/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.37  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.67/2.37  
% 5.67/2.37  %Foreground sorts:
% 5.67/2.37  
% 5.67/2.37  
% 5.67/2.37  %Background operators:
% 5.67/2.37  
% 5.67/2.37  
% 5.67/2.37  %Foreground operators:
% 5.67/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.37  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 5.67/2.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.67/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.67/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.67/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.67/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.67/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.67/2.37  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.37  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.37  tff('#skF_1', type, '#skF_1': $i).
% 5.67/2.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.67/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.67/2.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.67/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.67/2.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.67/2.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.67/2.37  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.67/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.67/2.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.67/2.37  
% 5.67/2.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.67/2.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 5.67/2.39  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 5.67/2.39  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.67/2.39  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.67/2.39  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 5.67/2.39  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.67/2.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.39  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.67/2.39  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.67/2.39  tff(c_45, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.67/2.39  tff(c_53, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_45])).
% 5.67/2.39  tff(c_103, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.67/2.39  tff(c_116, plain, (![A_74]: (r1_tarski(A_74, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_74, '#skF_2'))), inference(resolution, [status(thm)], [c_53, c_103])).
% 5.67/2.39  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.67/2.39  tff(c_230, plain, (![A_96, A_97]: (r1_tarski(A_96, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_96, A_97) | ~r1_tarski(A_97, '#skF_2'))), inference(resolution, [status(thm)], [c_116, c_10])).
% 5.67/2.39  tff(c_917, plain, (![A_200, C_201, B_202]: (r1_tarski(k3_xboole_0(A_200, C_201), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(B_202, '#skF_2') | ~r1_tarski(A_200, B_202))), inference(resolution, [status(thm)], [c_8, c_230])).
% 5.67/2.39  tff(c_941, plain, (![A_200, C_201]: (r1_tarski(k3_xboole_0(A_200, C_201), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_200, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_917])).
% 5.67/2.39  tff(c_30, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.67/2.39  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.67/2.39  tff(c_36, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.67/2.39  tff(c_1005, plain, (![B_210, A_211, C_212]: (v1_tops_2(B_210, A_211) | ~v1_tops_2(C_212, A_211) | ~r1_tarski(B_210, C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211)))) | ~m1_subset_1(B_210, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211)))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.67/2.39  tff(c_1217, plain, (![A_229, C_230, A_231, B_232]: (v1_tops_2(k3_xboole_0(A_229, C_230), A_231) | ~v1_tops_2(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_231)))) | ~m1_subset_1(k3_xboole_0(A_229, C_230), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_231)))) | ~l1_pre_topc(A_231) | ~r1_tarski(A_229, B_232))), inference(resolution, [status(thm)], [c_8, c_1005])).
% 5.67/2.39  tff(c_1224, plain, (![A_229, C_230]: (v1_tops_2(k3_xboole_0(A_229, C_230), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k3_xboole_0(A_229, C_230), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_229, '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1217])).
% 5.67/2.39  tff(c_1301, plain, (![A_241, C_242]: (v1_tops_2(k3_xboole_0(A_241, C_242), '#skF_1') | ~m1_subset_1(k3_xboole_0(A_241, C_242), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_241, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_1224])).
% 5.67/2.39  tff(c_1828, plain, (![A_306, C_307]: (v1_tops_2(k3_xboole_0(A_306, C_307), '#skF_1') | ~r1_tarski(A_306, '#skF_2') | ~r1_tarski(k3_xboole_0(A_306, C_307), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_30, c_1301])).
% 5.67/2.39  tff(c_1924, plain, (![A_308, C_309]: (v1_tops_2(k3_xboole_0(A_308, C_309), '#skF_1') | ~r1_tarski(A_308, '#skF_2'))), inference(resolution, [status(thm)], [c_941, c_1828])).
% 5.67/2.39  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.67/2.39  tff(c_132, plain, (![A_76, B_77, C_78]: (k9_subset_1(A_76, B_77, C_78)=k3_xboole_0(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.67/2.39  tff(c_140, plain, (![B_77]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_77, '#skF_3')=k3_xboole_0(B_77, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_132])).
% 5.67/2.39  tff(c_34, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.67/2.39  tff(c_142, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_34])).
% 5.67/2.39  tff(c_1927, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1924, c_142])).
% 5.67/2.39  tff(c_1931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1927])).
% 5.67/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.39  
% 5.67/2.39  Inference rules
% 5.67/2.39  ----------------------
% 5.67/2.39  #Ref     : 0
% 5.67/2.39  #Sup     : 457
% 5.67/2.39  #Fact    : 0
% 5.67/2.39  #Define  : 0
% 5.67/2.39  #Split   : 3
% 5.67/2.39  #Chain   : 0
% 5.67/2.39  #Close   : 0
% 5.67/2.39  
% 5.67/2.39  Ordering : KBO
% 5.67/2.39  
% 5.67/2.39  Simplification rules
% 5.67/2.39  ----------------------
% 5.67/2.39  #Subsume      : 51
% 5.67/2.39  #Demod        : 50
% 5.67/2.39  #Tautology    : 69
% 5.67/2.39  #SimpNegUnit  : 0
% 5.67/2.39  #BackRed      : 1
% 5.67/2.39  
% 5.67/2.39  #Partial instantiations: 0
% 5.67/2.39  #Strategies tried      : 1
% 5.67/2.39  
% 5.67/2.39  Timing (in seconds)
% 5.67/2.39  ----------------------
% 5.67/2.40  Preprocessing        : 0.53
% 5.67/2.40  Parsing              : 0.28
% 5.67/2.40  CNF conversion       : 0.04
% 5.67/2.40  Main loop            : 1.02
% 5.67/2.40  Inferencing          : 0.32
% 5.67/2.40  Reduction            : 0.30
% 5.67/2.40  Demodulation         : 0.22
% 5.67/2.40  BG Simplification    : 0.05
% 5.67/2.40  Subsumption          : 0.27
% 5.67/2.40  Abstraction          : 0.06
% 5.67/2.40  MUC search           : 0.00
% 5.67/2.40  Cooper               : 0.00
% 5.67/2.40  Total                : 1.59
% 5.67/2.40  Index Insertion      : 0.00
% 5.67/2.40  Index Deletion       : 0.00
% 5.67/2.40  Index Matching       : 0.00
% 5.67/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
