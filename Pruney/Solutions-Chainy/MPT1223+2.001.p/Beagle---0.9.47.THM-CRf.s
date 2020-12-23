%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:25 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   50 (  73 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 189 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & r1_tarski(C,B) )
                 => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( r2_hidden(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( v4_pre_topc(D,A)
                        & r1_tarski(B,D) )
                     => r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_86,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k2_pre_topc(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [C_49,A_50,B_51] :
      ( r2_hidden(C_49,A_50)
      | ~ r2_hidden(C_49,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_55,B_56,A_57] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_57)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(A_57))
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_55,A_57] :
      ( ~ m1_subset_1(A_55,k1_zfmisc_1(A_57))
      | r1_tarski(A_55,A_57) ) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_90,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k2_pre_topc(A_60,B_61),u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_86,c_76])).

tff(c_26,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_45,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_1,B_2,B_47] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_47)
      | ~ r1_tarski(A_1,B_47)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_28,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_808,plain,(
    ! [C_161,D_162,B_163,A_164] :
      ( r2_hidden(C_161,D_162)
      | ~ r1_tarski(B_163,D_162)
      | ~ v4_pre_topc(D_162,A_164)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ r2_hidden(C_161,k2_pre_topc(A_164,B_163))
      | ~ r2_hidden(C_161,u1_struct_0(A_164))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_842,plain,(
    ! [C_173,A_174] :
      ( r2_hidden(C_173,'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_174)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ r2_hidden(C_173,k2_pre_topc(A_174,'#skF_5'))
      | ~ r2_hidden(C_173,u1_struct_0(A_174))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_28,c_808])).

tff(c_1359,plain,(
    ! [A_232,B_233,A_234] :
      ( r2_hidden('#skF_1'(A_232,B_233),'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_234)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ r2_hidden('#skF_1'(A_232,B_233),u1_struct_0(A_234))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234)
      | ~ r1_tarski(A_232,k2_pre_topc(A_234,'#skF_5'))
      | r1_tarski(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_48,c_842])).

tff(c_11763,plain,(
    ! [A_728,B_729,A_730] :
      ( r2_hidden('#skF_1'(A_728,B_729),'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_730)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_730)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_730)))
      | ~ l1_pre_topc(A_730)
      | ~ r1_tarski(A_728,k2_pre_topc(A_730,'#skF_5'))
      | ~ r1_tarski(A_728,u1_struct_0(A_730))
      | r1_tarski(A_728,B_729) ) ),
    inference(resolution,[status(thm)],[c_48,c_1359])).

tff(c_11765,plain,(
    ! [A_728,B_729] :
      ( r2_hidden('#skF_1'(A_728,B_729),'#skF_4')
      | ~ v4_pre_topc('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_728,k2_pre_topc('#skF_3','#skF_5'))
      | ~ r1_tarski(A_728,u1_struct_0('#skF_3'))
      | r1_tarski(A_728,B_729) ) ),
    inference(resolution,[status(thm)],[c_32,c_11763])).

tff(c_12117,plain,(
    ! [A_748,B_749] :
      ( r2_hidden('#skF_1'(A_748,B_749),'#skF_4')
      | ~ r1_tarski(A_748,k2_pre_topc('#skF_3','#skF_5'))
      | ~ r1_tarski(A_748,u1_struct_0('#skF_3'))
      | r1_tarski(A_748,B_749) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_11765])).

tff(c_12186,plain,(
    ! [A_752] :
      ( ~ r1_tarski(A_752,k2_pre_topc('#skF_3','#skF_5'))
      | ~ r1_tarski(A_752,u1_struct_0('#skF_3'))
      | r1_tarski(A_752,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12117,c_4])).

tff(c_12212,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_12186])).

tff(c_12228,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_12212])).

tff(c_12243,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_12228])).

tff(c_12251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_12243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:29:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.49/4.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/4.12  
% 11.49/4.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/4.12  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 11.49/4.12  
% 11.49/4.12  %Foreground sorts:
% 11.49/4.12  
% 11.49/4.12  
% 11.49/4.12  %Background operators:
% 11.49/4.12  
% 11.49/4.12  
% 11.49/4.12  %Foreground operators:
% 11.49/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.49/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.49/4.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.49/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.49/4.12  tff('#skF_5', type, '#skF_5': $i).
% 11.49/4.12  tff('#skF_3', type, '#skF_3': $i).
% 11.49/4.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.49/4.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.49/4.12  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.49/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.49/4.12  tff('#skF_4', type, '#skF_4': $i).
% 11.49/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.49/4.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.49/4.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.49/4.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.49/4.12  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.49/4.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.49/4.12  
% 11.49/4.13  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 11.49/4.13  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.49/4.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.49/4.13  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.49/4.13  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 11.49/4.13  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.49/4.13  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.49/4.13  tff(c_86, plain, (![A_60, B_61]: (m1_subset_1(k2_pre_topc(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.49/4.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.49/4.13  tff(c_49, plain, (![C_49, A_50, B_51]: (r2_hidden(C_49, A_50) | ~r2_hidden(C_49, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.49/4.13  tff(c_65, plain, (![A_55, B_56, A_57]: (r2_hidden('#skF_1'(A_55, B_56), A_57) | ~m1_subset_1(A_55, k1_zfmisc_1(A_57)) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_6, c_49])).
% 11.49/4.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.49/4.13  tff(c_76, plain, (![A_55, A_57]: (~m1_subset_1(A_55, k1_zfmisc_1(A_57)) | r1_tarski(A_55, A_57))), inference(resolution, [status(thm)], [c_65, c_4])).
% 11.49/4.13  tff(c_90, plain, (![A_60, B_61]: (r1_tarski(k2_pre_topc(A_60, B_61), u1_struct_0(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_86, c_76])).
% 11.49/4.13  tff(c_26, plain, (~r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.49/4.13  tff(c_38, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.49/4.13  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_38])).
% 11.49/4.13  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.49/4.13  tff(c_30, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.49/4.13  tff(c_45, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.49/4.13  tff(c_48, plain, (![A_1, B_2, B_47]: (r2_hidden('#skF_1'(A_1, B_2), B_47) | ~r1_tarski(A_1, B_47) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_45])).
% 11.49/4.13  tff(c_28, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.49/4.13  tff(c_808, plain, (![C_161, D_162, B_163, A_164]: (r2_hidden(C_161, D_162) | ~r1_tarski(B_163, D_162) | ~v4_pre_topc(D_162, A_164) | ~m1_subset_1(D_162, k1_zfmisc_1(u1_struct_0(A_164))) | ~r2_hidden(C_161, k2_pre_topc(A_164, B_163)) | ~r2_hidden(C_161, u1_struct_0(A_164)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.49/4.13  tff(c_842, plain, (![C_173, A_174]: (r2_hidden(C_173, '#skF_4') | ~v4_pre_topc('#skF_4', A_174) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_174))) | ~r2_hidden(C_173, k2_pre_topc(A_174, '#skF_5')) | ~r2_hidden(C_173, u1_struct_0(A_174)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_28, c_808])).
% 11.49/4.13  tff(c_1359, plain, (![A_232, B_233, A_234]: (r2_hidden('#skF_1'(A_232, B_233), '#skF_4') | ~v4_pre_topc('#skF_4', A_234) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_234))) | ~r2_hidden('#skF_1'(A_232, B_233), u1_struct_0(A_234)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234) | ~r1_tarski(A_232, k2_pre_topc(A_234, '#skF_5')) | r1_tarski(A_232, B_233))), inference(resolution, [status(thm)], [c_48, c_842])).
% 11.49/4.13  tff(c_11763, plain, (![A_728, B_729, A_730]: (r2_hidden('#skF_1'(A_728, B_729), '#skF_4') | ~v4_pre_topc('#skF_4', A_730) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_730))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_730))) | ~l1_pre_topc(A_730) | ~r1_tarski(A_728, k2_pre_topc(A_730, '#skF_5')) | ~r1_tarski(A_728, u1_struct_0(A_730)) | r1_tarski(A_728, B_729))), inference(resolution, [status(thm)], [c_48, c_1359])).
% 11.49/4.13  tff(c_11765, plain, (![A_728, B_729]: (r2_hidden('#skF_1'(A_728, B_729), '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_728, k2_pre_topc('#skF_3', '#skF_5')) | ~r1_tarski(A_728, u1_struct_0('#skF_3')) | r1_tarski(A_728, B_729))), inference(resolution, [status(thm)], [c_32, c_11763])).
% 11.49/4.13  tff(c_12117, plain, (![A_748, B_749]: (r2_hidden('#skF_1'(A_748, B_749), '#skF_4') | ~r1_tarski(A_748, k2_pre_topc('#skF_3', '#skF_5')) | ~r1_tarski(A_748, u1_struct_0('#skF_3')) | r1_tarski(A_748, B_749))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_11765])).
% 11.49/4.13  tff(c_12186, plain, (![A_752]: (~r1_tarski(A_752, k2_pre_topc('#skF_3', '#skF_5')) | ~r1_tarski(A_752, u1_struct_0('#skF_3')) | r1_tarski(A_752, '#skF_4'))), inference(resolution, [status(thm)], [c_12117, c_4])).
% 11.49/4.13  tff(c_12212, plain, (~r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_43, c_12186])).
% 11.49/4.13  tff(c_12228, plain, (~r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_26, c_12212])).
% 11.49/4.13  tff(c_12243, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_90, c_12228])).
% 11.49/4.13  tff(c_12251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_12243])).
% 11.49/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/4.13  
% 11.49/4.13  Inference rules
% 11.49/4.13  ----------------------
% 11.49/4.13  #Ref     : 0
% 11.49/4.13  #Sup     : 3067
% 11.49/4.13  #Fact    : 0
% 11.49/4.13  #Define  : 0
% 11.49/4.13  #Split   : 25
% 11.49/4.13  #Chain   : 0
% 11.49/4.13  #Close   : 0
% 11.49/4.13  
% 11.49/4.13  Ordering : KBO
% 11.49/4.13  
% 11.49/4.13  Simplification rules
% 11.49/4.13  ----------------------
% 11.49/4.13  #Subsume      : 1896
% 11.49/4.13  #Demod        : 975
% 11.49/4.13  #Tautology    : 92
% 11.49/4.13  #SimpNegUnit  : 27
% 11.49/4.13  #BackRed      : 0
% 11.49/4.13  
% 11.49/4.13  #Partial instantiations: 0
% 11.49/4.13  #Strategies tried      : 1
% 11.49/4.13  
% 11.49/4.13  Timing (in seconds)
% 11.49/4.13  ----------------------
% 11.49/4.13  Preprocessing        : 0.31
% 11.49/4.13  Parsing              : 0.17
% 11.49/4.13  CNF conversion       : 0.02
% 11.49/4.13  Main loop            : 3.04
% 11.49/4.13  Inferencing          : 0.61
% 11.49/4.13  Reduction            : 0.64
% 11.49/4.13  Demodulation         : 0.40
% 11.49/4.13  BG Simplification    : 0.05
% 11.49/4.13  Subsumption          : 1.61
% 11.49/4.13  Abstraction          : 0.09
% 11.49/4.13  MUC search           : 0.00
% 11.49/4.13  Cooper               : 0.00
% 11.49/4.13  Total                : 3.37
% 11.49/4.13  Index Insertion      : 0.00
% 11.49/4.13  Index Deletion       : 0.00
% 11.49/4.13  Index Matching       : 0.00
% 11.49/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
